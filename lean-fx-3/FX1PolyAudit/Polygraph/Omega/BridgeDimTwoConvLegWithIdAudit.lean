import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.BridgeDimTwoConvLegWithId

/-! # FX1PolyAudit.Polygraph.Omega.BridgeDimTwoConvLegWithIdAudit — zero-axiom gate for the n=2 bridge conv
leg over the idCongr sibling (OMEGA bridge round, leg (ii) closure).

Per-declaration `#assert_no_axioms` on the strict-row injector, the right-unit mirror, the ported dim-1
collapse coherences, the boundary coherences, the generic middle-four rebracket, the interchange arm, the
twelve-arm step induction, the four-arm conv induction, the `bridgeDimTwoHoldsWithId` inhabitant, and the
closure marker. -/

namespace FX1PolyAudit

-- BridgeDimTwoConvLegWithId.lean
#assert_no_axioms FX1Poly.Polygraph.Omega.strictRowWithId
#assert_no_axioms FX1Poly.Polygraph.Omega.vcompIdRight_bridgedWithId
#assert_no_axioms FX1Poly.Polygraph.Omega.realizePathCellSig_boundarySource
#assert_no_axioms FX1Poly.Polygraph.Omega.realizePathCellSig_composePath_convWithId
#assert_no_axioms FX1Poly.Polygraph.Omega.toCellDimTwo_boundarySource_convWithId
#assert_no_axioms FX1Poly.Polygraph.Omega.toCellDimTwo_boundaryTarget_convWithId
#assert_no_axioms FX1Poly.Polygraph.Omega.vcompMiddleFourRebracket
#assert_no_axioms FX1Poly.Polygraph.Omega.bridgeInterchangeArm
#assert_no_axioms FX1Poly.Polygraph.Omega.toCellDimTwo_step_convWithId
#assert_no_axioms FX1Poly.Polygraph.Omega.toCellDimTwo_conv_convWithId
#assert_no_axioms FX1Poly.Polygraph.Omega.bridgeDimTwoHoldsWithId_proof
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega_bridgeDimTwoHoldsWithIdConvLegClosedR4

end FX1PolyAudit
