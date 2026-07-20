import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Net.ExtendedPetriInhibitor

/-! # FX1PolyAudit/Polygraph/Net/ExtendedPetriInhibitor — zero-axiom gate
    (NET-8 brick: extended Petri nets, the decidable extension taxonomy, the total
    2-counter Minsky → inhibitor-net encoding, and the inhibitor-reachability
    UNDECIDABILITY wall)

Per-declaration zero-axiom gate for the extended-net kit: the `XpnArcKind`/`XpnTransition`/
`XpnNet` carrier, the marking lookup/update primitives (`xpnNth`, `xpnIsZeroAt`,
`xpnSetZeroAt`, `xpnAddAt`, `xpnZeros`, `xpnOneHot`), firing with inhibitor zero-test guards
(`xpnAllGuardsZero`, `xpnFireEnabled`, `xpnApplyResets`, `xpnApplyTransferOne`,
`xpnApplyTransfers`, `xpnFireStep`), the guard-elimination and monotone-firing soundness
(`xpnFireEnabledElim`, `xpnFireStepPlainIsCvbFire`, `xpnPlainFireMonotone`), the decidable
extension taxonomy (`xpnExtensionCoverabilityDecidable`), the total Minsky encoding
(`XpnMinskyInstr`, `xpnInstrToTransitions`, `xpnAppendTransitions`, `xpnFoldInstrs`,
`xpnLength`, `xpnTransitionCount`, `xpnTwoCounterToInhibitorNet`), and the ground fires.

The reachability claims are WALLED (`xpnHasInhibitorReachability = false`,
`xpnHasResetReachability = false`, `xpnInhibitorUndecidableViaMinsky = false`): inhibitor-net
(and reset-net) reachability is UNDECIDABLE — the 2-counter Minsky halting problem reduces to
it via the total witness `xpnTwoCounterToInhibitorNet`, the non-monotone zero-test breaking
WSTS.  This is a genuine undecidability wall, stronger than the NET-4 provability wall
`FX1Poly.ComputerAlgebra.fxNet4_dicksonWall`.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Net.XpnArcKind
#assert_no_axioms FX1Poly.Polygraph.Net.XpnArcKind.plainArc
#assert_no_axioms FX1Poly.Polygraph.Net.XpnArcKind.resetArc
#assert_no_axioms FX1Poly.Polygraph.Net.XpnArcKind.transferArc
#assert_no_axioms FX1Poly.Polygraph.Net.XpnArcKind.inhibitorArc
#assert_no_axioms FX1Poly.Polygraph.Net.XpnTransition
#assert_no_axioms FX1Poly.Polygraph.Net.XpnTransition.mk
#assert_no_axioms FX1Poly.Polygraph.Net.XpnNet
#assert_no_axioms FX1Poly.Polygraph.Net.XpnNet.mk
#assert_no_axioms FX1Poly.Polygraph.Net.xpnNth
#assert_no_axioms FX1Poly.Polygraph.Net.xpnIsZeroAt
#assert_no_axioms FX1Poly.Polygraph.Net.xpnSetZeroAt
#assert_no_axioms FX1Poly.Polygraph.Net.xpnAddAt
#assert_no_axioms FX1Poly.Polygraph.Net.xpnZeros
#assert_no_axioms FX1Poly.Polygraph.Net.xpnOneHot
#assert_no_axioms FX1Poly.Polygraph.Net.xpnAllGuardsZero
#assert_no_axioms FX1Poly.Polygraph.Net.xpnFireEnabled
#assert_no_axioms FX1Poly.Polygraph.Net.xpnApplyResets
#assert_no_axioms FX1Poly.Polygraph.Net.xpnApplyTransferOne
#assert_no_axioms FX1Poly.Polygraph.Net.xpnApplyTransfers
#assert_no_axioms FX1Poly.Polygraph.Net.xpnFireStep
#assert_no_axioms FX1Poly.Polygraph.Net.xpnFireEnabledElim
#assert_no_axioms FX1Poly.Polygraph.Net.xpnFireStepPlainIsCvbFire
#assert_no_axioms FX1Poly.Polygraph.Net.xpnPlainFireMonotone
#assert_no_axioms FX1Poly.Polygraph.Net.xpnExtensionCoverabilityDecidable
#assert_no_axioms FX1Poly.Polygraph.Net.XpnMinskyInstr
#assert_no_axioms FX1Poly.Polygraph.Net.XpnMinskyInstr.inc
#assert_no_axioms FX1Poly.Polygraph.Net.XpnMinskyInstr.dec
#assert_no_axioms FX1Poly.Polygraph.Net.xpnInstrToTransitions
#assert_no_axioms FX1Poly.Polygraph.Net.xpnAppendTransitions
#assert_no_axioms FX1Poly.Polygraph.Net.xpnFoldInstrs
#assert_no_axioms FX1Poly.Polygraph.Net.xpnLength
#assert_no_axioms FX1Poly.Polygraph.Net.xpnTransitionCount
#assert_no_axioms FX1Poly.Polygraph.Net.xpnTwoCounterToInhibitorNet
#assert_no_axioms FX1Poly.Polygraph.Net.xpnHasInhibitorReachability
#assert_no_axioms FX1Poly.Polygraph.Net.xpnHasResetReachability
#assert_no_axioms FX1Poly.Polygraph.Net.xpnInhibitorUndecidableViaMinsky
#assert_no_axioms FX1Poly.Polygraph.Net.xpnHasDecidableExtensionTaxonomy
#assert_no_axioms FX1Poly.Polygraph.Net.xpnHasTotalMinskyEncoding
#assert_no_axioms FX1Poly.Polygraph.Net.xpnHasResetTransferMonotoneFiring
#assert_no_axioms FX1Poly.Polygraph.Net.xpnPlainEnabledTransition
#assert_no_axioms FX1Poly.Polygraph.Net.xpnInhibitedTransition
#assert_no_axioms FX1Poly.Polygraph.Net.xpnResetTransition
#assert_no_axioms FX1Poly.Polygraph.Net.xpnTransferTransition
#assert_no_axioms FX1Poly.Polygraph.Net.xpnExampleProgram
#assert_no_axioms FX1Poly.Polygraph.Net.xpnExampleNet
#assert_no_axioms FX1Poly.Polygraph.Net.xpnFireEnabledPlainTrue
#assert_no_axioms FX1Poly.Polygraph.Net.xpnFireEnabledNotCoveredFalse
#assert_no_axioms FX1Poly.Polygraph.Net.xpnFireEnabledInhibitorClear
#assert_no_axioms FX1Poly.Polygraph.Net.xpnFireEnabledInhibitorBlocked
#assert_no_axioms FX1Poly.Polygraph.Net.xpnInhibitorNonMonotone
#assert_no_axioms FX1Poly.Polygraph.Net.xpnFireStepComputes
#assert_no_axioms FX1Poly.Polygraph.Net.xpnFireStepResetZeroes
#assert_no_axioms FX1Poly.Polygraph.Net.xpnFireStepTransferMoves
#assert_no_axioms FX1Poly.Polygraph.Net.xpnTaxonomyPlain
#assert_no_axioms FX1Poly.Polygraph.Net.xpnTaxonomyReset
#assert_no_axioms FX1Poly.Polygraph.Net.xpnTaxonomyTransfer
#assert_no_axioms FX1Poly.Polygraph.Net.xpnTaxonomyInhibitor
#assert_no_axioms FX1Poly.Polygraph.Net.xpnDecHasInhibitorGuard
#assert_no_axioms FX1Poly.Polygraph.Net.xpnExampleNetPlaceCount
#assert_no_axioms FX1Poly.Polygraph.Net.xpnExampleNetTransitionCount
#assert_no_axioms FX1Poly.Polygraph.Net.xpnInhibitorWallIsFalse
#assert_no_axioms FX1Poly.Polygraph.Net.xpnResetWallIsFalse
#assert_no_axioms FX1Poly.Polygraph.Net.xpnInhibitorUndecidableIsFalse
#assert_no_axioms FX1Poly.Polygraph.Net.xpnHasDecidableExtensionTaxonomyIsTrue
#assert_no_axioms FX1Poly.Polygraph.Net.xpnHasTotalMinskyEncodingIsTrue
#assert_no_axioms FX1Poly.Polygraph.Net.xpnHasResetTransferMonotoneFiringIsTrue

end FX1PolyAudit
