import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringCupPositionEmbedding

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringCupPositionEmbedding — zero-axiom gate
(FC-3 r33, B5 keystone: the concrete seed-agnostic cup position embedding)

Per-declaration zero-axiom gate for the string CONCRETE cup position embedding over the walking ADJOINT-TRIPLE
signature: the named fold `stringCupPositionEmbedding` and its two order-embedding facts
(`stringCupPositionEmbedding_isWireOrderEmbedding` / `stringCupPositionEmbedding_imageCover`), a byte-identical
token-swap of the walking-adjunction `CupPositionEmbedding` over the signature-BLIND order-embedding substrate.
Every declaration must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  The
project `#assert_no_axioms` macro is fuel-based; the independent `#print axioms` lines below are the trusted
cross-check. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringCupPositionEmbedding_isWireOrderEmbedding
#assert_no_axioms FX1Poly.Polygraph.stringCupPositionEmbedding_imageCover
#assert_no_axioms FX1Poly.Polygraph.fxString_hasConcreteCupPositionEmbedding

-- independent cross-check (the fuel macro is not trusted alone)
#print axioms FX1Poly.Polygraph.stringCupPositionEmbedding_isWireOrderEmbedding
#print axioms FX1Poly.Polygraph.stringCupPositionEmbedding_imageCover
#print axioms FX1Poly.Polygraph.fxString_hasConcreteCupPositionEmbedding

end FX1PolyAudit
