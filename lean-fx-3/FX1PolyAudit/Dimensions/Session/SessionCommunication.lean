import FX1PolyAudit.DependencyAudit
import FX1Poly.Dimensions.Session.SessionCommunication

/-! # FX1PolyAudit.Dimensions.Session.SessionCommunication — zero-axiom gate (mirror shard, region-D restructure) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Modal.CommStep
#assert_no_axioms FX1Poly.Modal.CommStep.preservesDuality
#assert_no_axioms FX1Poly.Modal.dualPairProgresses
#assert_no_axioms FX1Poly.Modal.dualChannelProgressesOrIsDone
#assert_no_axioms FX1Poly.Modal.endChannelIsTerminal
#assert_no_axioms FX1Poly.Modal.concreteChannelStep
#assert_no_axioms FX1Poly.Modal.sendSendStuck
#assert_no_axioms FX1Poly.Modal.sendSendIsNotDual
#assert_no_axioms FX1Poly.Modal.nonDualChannelDeadlocks
#assert_no_axioms FX1Poly.Modal.dualPartnerFixesTheMismatchedDeadlock
#assert_no_axioms FX1Poly.Modal.dualityIsNecessaryForDeadlockFreedom

end FX1PolyAudit
