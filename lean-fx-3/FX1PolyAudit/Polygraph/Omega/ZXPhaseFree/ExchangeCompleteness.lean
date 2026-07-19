import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.ZXPhaseFree.ExchangeCompleteness

/-! # FX1PolyAudit.Polygraph.Omega.ZXPhaseFree.ExchangeCompleteness — zero-axiom gate
(THE RIGHT-FIRST EXCHANGE MOVE + gate re-run + GENERAL-k PARALLEL FUSION)

Per-declaration zero-axiom gate for the exchange brick: the exchange window family
(`zxeExchangeLhs`/`zxeExchangeRhs`) with STRUCTURAL all-arity soundness through the
interchange theorem (`zxeExchangeBundle`), THE EXCHANGE-EXTENDED CONGRUENCE
(`ZxeWindowMove`/`ZxeStep`/`ZxeConv` in the seed's exact shapes) with soundness
`zxeConvSound`, refutation bridge `zxeConvSpanEqB`, embeddings `zxeOfZxrConv` /
`zxeOfZxpConv`, the ported pad-lifting congruence `zxeConvLift` + plain-context
helpers, the fired exchange (`zxeExchangeConv`, `zxeRightFirstExchangeHolds` — the
ladder's walled statement shape holds over `ZxeConv`), the k = 1/2/3 ladder
transports, THE GATE RE-RUN (exchange invisibility `zxeExchangeFoldBalanced`, the
extended fold engine, the carried collapse theorem, the general mod-2 delta
saturation with kernel span/lattice pins, verdict CLEAN), GENERAL-k PARALLEL FUSION
both colours all arities (`zxeParallelFusionStepZ/X` right-corner absorption
recursion, `zxeParallelFusionZ/X`, combined `zxeParallelFusion`) with the k = 4 and
k = 5 fires and the independent kernel span cross-check, and the (D) partials:
`zxeCompletenessStatement` minted owner-FALSE over `ZxeConv` (the ZxrConv original
stays owner-false in FusionRepair; delta = exchange admissibility in `ZxrConv`,
recorded open via `zxeExchangeAdmissibleInZxrConvIsProven := false`), identity-wire
absorption lemmas, the conditional decision corollary, and the negative control
`zxeBigColourNotConv`.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`,
`omega`, `WellFounded.fix`, `funext`.  Built by the FX1PolyAudit lib glob;
AuditAll registration is a later round's bookkeeping (AuditAll untouched per this
round's commission). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeExchangeLhs
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeExchangeRhs
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeExchangeLhsCodArity
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeExchangeRhsCodArity
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeExchangeLhsWF
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeExchangeRhsWF
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeExchangeLhsDenoteEquiv
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeExchangeRhsDenoteEquiv
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeExchangeBundle

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.ZxeWindowMove
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.ZxeWindowMove.base
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.ZxeWindowMove.rightFirstExchange
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeWindowMoveBundle
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.ZxeStep
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.ZxeStep.pad
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeStepBundle
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.ZxeConv
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.ZxeConv.step
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.ZxeConv.refl
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.ZxeConv.symm
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.ZxeConv.trans
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeConvSound
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeConvSpanEqB
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeOfZxrConv
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeOfZxpConv

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeConvLift
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxePadPlainLayers
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeStepConv
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeLiftConv

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeExchangeConv
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeRightFirstExchangeStatement
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeRightFirstExchangeHolds
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeParallelFusionOneWireZ
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeParallelFusionOneWireX
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeParallelFusionTwoWireZ
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeParallelFusionTwoWireX
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeParallelFusionThreeWireZ
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeParallelFusionThreeWireX
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeEtaExpandWireZ
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeEtaExpandWireX

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeExchangeFoldBalanced
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeWindowMoveFoldEq
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeStepFoldEq
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeConvFoldEq
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeBalancedWeightCollapse
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeBalancedWeightFoldZero
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeBigSpiderExchangeBalanced
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeExchangeWireFoldShift
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeExchangeDeltaGeneral
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeExchangeDeltaEven
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeExchangeDeltaOdd
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeExchangeDeltaCases
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeExtendedDeltaTable
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeExtendedDeltaSpanBasisPin
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeIsPreservedExactlyLegsParityB
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxePreservedLatticeReclassified
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeLegsParityOrthogonalExchangeDelta
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeGateVerdictIsClean

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeParallelFusionStepZ
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeParallelFusionStepX
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeParallelFusionZ
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeParallelFusionX
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeParallelFusion
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeParallelFusionFourWireZFire
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeParallelFusionFiveWireZFire
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeParallelFusionFiveWireXFire
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeParallelFusionFiveWireSpanPin

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeCompletenessStatement
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeCompletenessIsProven
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeExchangeAdmissibleInZxrConvIsProven
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeStripLeadingWireLayer
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeStripTrailingWireLayer
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeDecisionUnderCompleteness
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeBigColourNotConv
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeHasExchangeMove
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxeGeneralKFusionLanded

end FX1PolyAudit
