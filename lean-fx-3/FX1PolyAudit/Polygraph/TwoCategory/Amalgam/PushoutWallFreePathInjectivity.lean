import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWallFreePathInjectivity

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutWallFreePathInjectivity — zero-axiom gate for the path-level
right-coprojection 1-cell injectivity via word reflection (WP-AMALG-2 r10, B1)

Per-declaration zero-axiom gate for the modality injectivity, the monad word reader, the coprojection word law, the
retag-cancellation, the word-recovery injectivity, and the path injectivity.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.mapModality_inclRight_injective
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadPathWord
#assert_no_axioms FX1Poly.Polygraph.Amalgam.mapPath_inclRight_word
#assert_no_axioms FX1Poly.Polygraph.Amalgam.mapEmbedRight_injective
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadPathWord_injective
#assert_no_axioms FX1Poly.Polygraph.Amalgam.mapPath_inclRight_injective
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasWallFreePathInjectivity

end FX1PolyAudit
