import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Corpus.Smoke.RawIotaEtaOperationalSN

/-! # FX1PolyAudit.Typed.Corpus.Smoke.RawIotaEtaOperationalSN

Zero-axiom audit shard mirroring kernel module `FX1Poly.Typed.Corpus.Smoke.RawIotaEtaOperationalSN`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Operational SN of the ι∪η fragment (Tait-free), the RPO-leg SN endpoint for the parity matrix:
-- harvest of iotaEtaFullStep_wellFounded via the generic relation-polymorphic Acc lemmas
-- (accessibleElementHasNoInfiniteChain / accessibleElementNotSelfRelated).  iotaEta_noInfiniteReduction:
-- NO infinite ι∪η reduction sequence, for EVERY raw term, no typing hypothesis (vs β's Ω/tripler which DO
-- diverge as raw terms).  irreflexive: no 1-cycle.  no_two_cycle: no 2-cycle a⟷b, via a constructed
-- alternating chain (role-swapping recursion, no parity arithmetic) fed to the no-infinite-reduction lemma.
#assert_no_axioms FX1Poly.Core.iotaEta_noInfiniteReduction

#assert_no_axioms FX1Poly.Core.IotaEtaStep.irreflexive

#assert_no_axioms FX1Poly.Core.alternatingSequence_steps

#assert_no_axioms FX1Poly.Core.IotaEtaStep.no_two_cycle

end FX1PolyAudit
