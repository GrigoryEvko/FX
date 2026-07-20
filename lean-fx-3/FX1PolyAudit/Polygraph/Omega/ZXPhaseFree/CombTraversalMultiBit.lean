import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.ZXPhaseFree.CombTraversalMultiBit

/-! # FX1PolyAudit.Polygraph.Omega.ZXPhaseFree.CombTraversalMultiBit — zero-axiom
gate (the two-bit comb traversal and its fused codomain)

Per-declaration zero-axiom gate for the multi-bit comb-traversal round: the
explicit-form pin of the two-bit comb (`zxmTwoBitCombLayers`), the twelve-move
two-bit traversal (`zxmCombTraversalTwoBit`) and its fused-codomain form
(`zxmCombTraversalTwoBitFused`), the fire, the three kernel span pins, the two
live content markers, and the owner-false general-comb-traversal marker.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`,
`omega`, `WellFounded.fix`, `funext`.  Built by the FX1PolyAudit lib glob;
AuditAll registration is a later round's bookkeeping (AuditAll untouched per this
round's commission). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxmTwoBitCombLayers
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxmCombTraversalTwoBit
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxmCombTraversalTwoBitFused
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxmCombTraversalTwoBitFire
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxmCombTraversalTwoBitSpanPin
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxmCombTraversalTwoBitFusedSpanPin
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxmCopyStateFusedSpanPin
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxmHasTwoBitTraversal
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxmHasFusedCodomain
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxmHasGeneralCombTraversal

end FX1PolyAudit
