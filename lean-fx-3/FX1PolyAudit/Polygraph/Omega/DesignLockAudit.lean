import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.DesignLock

/-! # FX1PolyAudit.Polygraph.Omega.DesignLockAudit — zero-axiom gate for the OMEGA-1 r1 design lock + the
n=2 bridge / n=1 collapse STATEMENTS.

Per-declaration `#assert_no_axioms` on the design-lock classifier and markers, and on the forward-declared
bridge / collapse propositions.  A forward-declared Prop `def` introduces no axiom (it is a proposition, not a
proof), so the twin confirms r1 ships statements without smuggling any axiom.  Every declaration must be free of
`propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- DesignLock.lean
#assert_no_axioms FX1Poly.Polygraph.Omega.OmegaCarrierDecision
#assert_no_axioms FX1Poly.Polygraph.Omega.omegaCarrierDecision_chosen_ne_banned
#assert_no_axioms FX1Poly.Polygraph.Omega.omega1CarrierChoice
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega_omega1R1Complete
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega_carrierIsExtrinsicCandidateTwo

-- BridgeDimTwo.lean (the n=2 bridge STATEMENT)
#assert_no_axioms FX1Poly.Polygraph.Omega.signatureGenLabel
#assert_no_axioms FX1Poly.Polygraph.Omega.computadOfSignature
#assert_no_axioms FX1Poly.Polygraph.Omega.DimTwoTranslation
#assert_no_axioms FX1Poly.Polygraph.Omega.bridgeDimTwoHolds
-- BridgeDimTwo.lean — the r2 translation + PROVEN forward-size leg (B2)
#assert_no_axioms FX1Poly.Polygraph.Omega.realizePathCellSig
#assert_no_axioms FX1Poly.Polygraph.Omega.toCellDimTwo
#assert_no_axioms FX1Poly.Polygraph.Omega.toCellDimTwo_size
#assert_no_axioms FX1Poly.Polygraph.Omega.bridgeDimTwoForwardSize

-- CollapseDimOne.lean (the n=1 collapse STATEMENT + the build map)
#assert_no_axioms FX1Poly.Polygraph.Omega.graphGenLabel
#assert_no_axioms FX1Poly.Polygraph.Omega.computadOfGraph
#assert_no_axioms FX1Poly.Polygraph.Omega.realizePathCell
#assert_no_axioms FX1Poly.Polygraph.Omega.dimOneCollapsesToPath
#assert_no_axioms FX1Poly.Polygraph.Omega.dimZeroBoundaryIsMode
#assert_no_axioms FX1Poly.Polygraph.Omega.realizePathCell_boundarySource
#assert_no_axioms FX1Poly.Polygraph.Omega.realizePath_composePath_conv
#assert_no_axioms FX1Poly.Polygraph.Omega.oneCellCollapse_vcompClosed

-- CollapseDimOne.lean — the dim-1 collapse refutation (OMEGA-1 r2, B1)
#assert_no_axioms FX1Poly.Polygraph.Omega.skeletonGenAcc
#assert_no_axioms FX1Poly.Polygraph.Omega.oneCellGenList
#assert_no_axioms FX1Poly.Polygraph.Omega.dimOneGenListInvariant
#assert_no_axioms FX1Poly.Polygraph.Omega.dimOneGenListInvariant_trivial_succSucc
#assert_no_axioms FX1Poly.Polygraph.Omega.dimOneGenListInvariant_vcompAssoc
#assert_no_axioms FX1Poly.Polygraph.Omega.dimOneGenListInvariant_vcompUnitLeft
#assert_no_axioms FX1Poly.Polygraph.Omega.dimOneGenListInvariant_vcompUnitRight
#assert_no_axioms FX1Poly.Polygraph.Omega.dimOneGenListInvariant_isSaturatedCongruence
#assert_no_axioms FX1Poly.Polygraph.Omega.oneCellGenAcc_of_conv
#assert_no_axioms FX1Poly.Polygraph.Omega.refutingGraph
#assert_no_axioms FX1Poly.Polygraph.Omega.junkCell
#assert_no_axioms FX1Poly.Polygraph.Omega.skeletonModeValue
#assert_no_axioms FX1Poly.Polygraph.Omega.genAtomSourceCanonicalProp
#assert_no_axioms FX1Poly.Polygraph.Omega.allSourceCanonicalProp
#assert_no_axioms FX1Poly.Polygraph.Omega.realizePathCell_allSourceCanonical
#assert_no_axioms FX1Poly.Polygraph.Omega.junkCell_not_allSourceCanonical
#assert_no_axioms FX1Poly.Polygraph.Omega.dimOneCollapse_not_unconditional

end FX1PolyAudit
