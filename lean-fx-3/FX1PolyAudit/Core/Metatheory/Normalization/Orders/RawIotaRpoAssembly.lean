import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Metatheory.Normalization.Orders.RawIotaRpoAssembly

/-! # FX1PolyAudit.Core.Metatheory.Normalization.Orders.RawIotaRpoAssembly

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Metatheory.Normalization.Orders.RawIotaRpoAssembly`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Oriented root-ι SN assembly (Phase-Z re-scope EXECUTED): unify the non-recursive arms + the
-- listElim-cons recursive arm into ONE order over the ORIENTED fragment of the CANONICAL
-- FX1Poly.Core.IotaHeadStep (IotaOrientedHeadStep = IotaHeadStep ∧ the isNatRecursorSuccRedex guard is
-- false — the two Phase-Z SUBSTITUTING natElim/natRec succ-iotas join the β-imported boundary, exactly
-- betaNotOrientableByErasure's situation). iotaGenRank bumps optionMatch/eitherMatch to rank 2 (their
-- reduct app(branch,value) has head gen_app, which outranks the redex head under the recursive-arm
-- precedence — wrong direction; the bump fixes it). rpoOrientsAppliedFirst/Second orient the 3
-- applied-branch arms; IotaHeadStep.rpoEmbeds covers the 14 oriented arms (the 2 substituting arms
-- discharge via Bool.noConfusion on the guard). iotaOrientedHeadStep_wellFounded: the oriented root-ι
-- fragment is SN by ONE RPO via Subrelation.wf + InvImage.wf eraseToRose, Tait-free (the unification).
#assert_no_axioms FX1Poly.Core.RawIotaRpo.iotaGenPrecedence_wellFounded

#assert_no_axioms FX1Poly.Core.RawIotaRpo.rpoOrientsAppliedFirst

#assert_no_axioms FX1Poly.Core.RawIotaRpo.rpoOrientsAppliedSecond

#assert_no_axioms FX1Poly.Core.RawIotaRpo.iotaGenRpoWellFounded

#assert_no_axioms FX1Poly.Core.RawTerm.isNatRecursorSuccRedex

#assert_no_axioms FX1Poly.Core.IotaHeadStep.rpoEmbeds

#assert_no_axioms FX1Poly.Core.iotaOrientedHeadStep_wellFounded

#assert_no_axioms FX1Poly.Core.IotaOrientedHeadStep.isStronglyNormalizing

#assert_no_axioms FX1Poly.Core.IotaOrientedHeadStep.listElimConsSmoke

end FX1PolyAudit
