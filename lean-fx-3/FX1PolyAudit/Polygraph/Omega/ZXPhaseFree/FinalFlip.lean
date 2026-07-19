import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.ZXPhaseFree.FinalFlip

/-! # FX1PolyAudit.Polygraph.Omega.ZXPhaseFree.FinalFlip — zero-axiom gate
(the generator-transport round: elementary row operations as normal-form
conversions)

Per-declaration zero-axiom gate for the transport brick: the row-list
concatenation kit with width/membership/span transport, the comb whisker-shift
and gadget fission, THE ZERO-ROW DELETION WHOLE (`zxfZeroCombTail`,
`zxfZeroCombCollapse`, `zxfNormalFormZeroRowDrop` + fire + span pin), the two
comb-move residual statements, THE CONDITIONAL TRANSPORT ASSEMBLY
(duplication, duplication-out, span-member absorption, comb-past-fold,
extension/shrinking, `zxfTransportOfCombMoves`), the birth-side conjugation
bricks (`zxfCreatesCrossInsert`, `zxfCreatesCnotInsert`), the three proven
crossing-ride windows plus the merge-chain reassociation, the TT wall
(statement + span pin + owner false), and the honest marker ledger.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`,
`omega`, `WellFounded.fix`, `funext`.  Built by the FX1PolyAudit lib glob;
AuditAll registration is a later round's bookkeeping (AuditAll untouched per
this round's commission). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxfCatRows
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxfCatRowsAllWidth
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxfGeneratorBlockLayersCat
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxfRowMemCatLeft
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxfRowMemCatRight
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxfMemSpanCatRight
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxfMemSpanCatLeft
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxfCombLayersShift
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxfPadNoContext
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxfGadgetLayers
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxfCombLayersCons

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxfZeroCombTail
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxfZeroCombCollapse
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxfNormalFormZeroRowDrop
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxfZeroRowDropFire
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxfZeroRowDropFireSpanPin

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxfCombSwapStatement
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxfCombXorAbsorbStatement
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxfCombWFAt
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxfCombCodAt
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxfLiftUnder
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxfLiftAfter
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxfCombDuplicate
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxfCombDupOut
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxfCombAbsorb
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxfCatRowsNilRight
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxfCombPastBlocks
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxfBlocksExtend
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxfBlocksShrink
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxfTransportOfCombMoves

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxfCreatesCrossInsert
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxfCrossWindowFF
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxfCreatesCnotInsert
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxfCrossWindowFT
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxfCrossWindowTF
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxfCrossIntoMergeChain
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxfCrossWindowTTStatement
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxfCrossWindowTTSpanPin
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxfCrossWindowTTIsProven

#assert_no_axioms
  FX1Poly.Polygraph.Omega.ZXPhaseFree.zxfHasTransportConditionalAssembly
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxfCombSwapIsProven
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxfCombXorAbsorbIsProven
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxfGeneratorTransportIsProven
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxfHasFullDecision

end FX1PolyAudit
