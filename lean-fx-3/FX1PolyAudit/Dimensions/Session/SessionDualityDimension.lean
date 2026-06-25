import FX1PolyAudit.DependencyAudit
import FX1Poly.Dimensions.Session.SessionDualityDimension

/-! # FX1PolyAudit.Dimensions.Session.SessionDualityDimension — zero-axiom gate (mirror shard, region-D restructure) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Modal.SessionType
#assert_no_axioms FX1Poly.Modal.SessionType.dual
#assert_no_axioms FX1Poly.Modal.dual_endSession
#assert_no_axioms FX1Poly.Modal.dual_send
#assert_no_axioms FX1Poly.Modal.dual_receive
#assert_no_axioms FX1Poly.Modal.dual_selectChoice
#assert_no_axioms FX1Poly.Modal.dual_branchOffer
#assert_no_axioms FX1Poly.Modal.SessionType.dual_involutive
#assert_no_axioms FX1Poly.Modal.SessionType.dual_injective
#assert_no_axioms FX1Poly.Modal.selfDual_iff_endSession
#assert_no_axioms FX1Poly.Modal.sessionDualityIsInvolutionButNotIdentity

end FX1PolyAudit
