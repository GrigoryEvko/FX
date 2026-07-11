import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescTConnectCupChain

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescTConnectCupChain — zero-axiom gate (BRAUER r26, the CUP chain
factorization + position kit)

Per-declaration zero-axiom gate for the CUP chain: the six-phase factorization (`foldFactorsThroughCup`), the
`expandCupTopPairs` getAt kit (`expandCupTopPairs_getAt_fst` / `_snd`), the append/length re-proofs
(`natListGetAtAppendRightCup`, `natListAppendNil`, `natListLengthAppend`, `natAddLeftCancelCup`), the circle-phase
open-wire preservation (`circleFold_openWires`), the post-cap-post-middle width (`cupChainS3Width`), the abstract-state
weld (`cupArcConnectViaState`), the GENERAL per-arc CUP-class T-CONNECT (`cupArcConnect_general`) and its
boundary-matching lift (`cupArcMatching_general`), the firing probe, and the ingredient markers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.foldFactorsThroughCup
#assert_no_axioms FX1Poly.Polygraph.expandCupTopPairs_getAt_fst
#assert_no_axioms FX1Poly.Polygraph.expandCupTopPairs_getAt_snd
#assert_no_axioms FX1Poly.Polygraph.natListGetAtAppendRightCup
#assert_no_axioms FX1Poly.Polygraph.natListAppendNil
#assert_no_axioms FX1Poly.Polygraph.natListLengthAppend
#assert_no_axioms FX1Poly.Polygraph.circleFold_openWires
#assert_no_axioms FX1Poly.Polygraph.natAddLeftCancelCup
#assert_no_axioms FX1Poly.Polygraph.cupChainS3Width
#assert_no_axioms FX1Poly.Polygraph.cupArcConnectViaState
#assert_no_axioms FX1Poly.Polygraph.cupArcConnect_general
#assert_no_axioms FX1Poly.Polygraph.cupArcMatching_general
#assert_no_axioms FX1Poly.Polygraph.cupArcMatching_firesAdversarialB
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasCupChainFactorKit
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasCupClassTConnect

end FX1PolyAudit
