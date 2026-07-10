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

-- CollapseDimOne.lean (the n=1 collapse STATEMENT + the build map)
#assert_no_axioms FX1Poly.Polygraph.Omega.graphGenLabel
#assert_no_axioms FX1Poly.Polygraph.Omega.computadOfGraph
#assert_no_axioms FX1Poly.Polygraph.Omega.realizePathCell
#assert_no_axioms FX1Poly.Polygraph.Omega.dimOneCollapsesToPath
#assert_no_axioms FX1Poly.Polygraph.Omega.dimZeroBoundaryIsMode

end FX1PolyAudit
