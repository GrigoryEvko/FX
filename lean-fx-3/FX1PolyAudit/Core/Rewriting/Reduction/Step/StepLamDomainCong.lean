import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.Reduction.Step.StepLamDomainCong

/-! # FX1PolyAudit.Core.Rewriting.Reduction.Step.StepLamDomainCong

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Rewriting.Reduction.Step.StepLamDomainCong`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The lambda-domain-replay congruence `StepStar.lamDomainCong` — the one-hole-context instance of
-- `StepStar.congAt` at the `gen_lam` head child — relocated to the bespoke-`Step.eta`-free home
-- `FX1Poly/Core/StepLamDomainCong.lean` so the native table beta-eta confluence consumes it WITHOUT
-- importing the deletable bespoke βη cluster.  It replays the convertible annotations A ↝* C ↜* B
-- through the lambda domain child to join `lam A b` and `lam B b` at `lam C b` (the eta-lam-vs-beta
-- critical pair); root-only η chains could NOT lift, β/ι's congruence closure is load-bearing.
#assert_no_axioms FX1Poly.Core.StepStar.lamDomainCong

end FX1PolyAudit
