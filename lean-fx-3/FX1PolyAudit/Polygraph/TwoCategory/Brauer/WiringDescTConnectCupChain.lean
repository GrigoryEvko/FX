import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescTConnectCupChain

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescTConnectCupChain — zero-axiom gate (BRAUER r26, the CUP chain
factorization + position kit)

Per-declaration zero-axiom gate for the CUP-chain kit: the six-phase factorization through the cup block
(`foldFactorsThroughCup`), the `expandCupTopPairs` getAt kit (`expandCupTopPairs_getAt_fst` / `_snd`), the append-right
read (`natListGetAtAppendRightCup`), and the ingredient marker.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.foldFactorsThroughCup
#assert_no_axioms FX1Poly.Polygraph.expandCupTopPairs_getAt_fst
#assert_no_axioms FX1Poly.Polygraph.expandCupTopPairs_getAt_snd
#assert_no_axioms FX1Poly.Polygraph.natListGetAtAppendRightCup
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasCupChainFactorKit

end FX1PolyAudit
