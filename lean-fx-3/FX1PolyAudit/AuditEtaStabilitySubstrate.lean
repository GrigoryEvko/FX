import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.EtaStabilitySubstrate

/-! # FX1PolyAudit/AuditEtaStabilitySubstrate — ETA-T5 inc-4.3a shard

Per-declaration zero-axiom gate for the pointwise-star spine relation
and the stability bricks: embeddings, sequentialization,
renaming/weakening transport, the composed-read lookup bricks, the
supplied scrutinee hypothesis machinery, the payload-read
preservation, and the slot-replacement brick.  Must be free of
`propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

/-! ## The relation and transport -/

#assert_no_axioms FX1Poly.Core.EtaChildrenPointwiseStar.refl
#assert_no_axioms FX1Poly.Core.EtaChildrenPointwiseStar.ofPointwise
#assert_no_axioms FX1Poly.Core.EtaChildrenPointwiseStar.ofChildrenStep
#assert_no_axioms FX1Poly.Core.EtaChildrenPointwiseStar.toSequentialStar
#assert_no_axioms FX1Poly.Core.EtaChildrenPointwiseStar.rename
#assert_no_axioms FX1Poly.Core.EtaChildrenPointwiseStar.weakenSpineBy
#assert_no_axioms FX1Poly.Core.StepEtaOverTableStar.weakenByLift

/-! ## Lookup bricks -/

#assert_no_axioms FX1Poly.Core.EtaChildrenPointwiseStar.lookupAtShiftZeroRelated
#assert_no_axioms FX1Poly.Core.EtaChildrenPointwiseStar.lookupAtShiftOneRelated
#assert_no_axioms FX1Poly.Core.EtaChildrenPointwiseStar.lookupAtShiftTwoRelated

/-! ## Scrutinee, payload, and replacement bricks -/

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.scrutineeTermAt?_etaRelated
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.scrutineeCellExtraction_etaRelated
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.resolvePayloadSource?_etaPreserved
#assert_no_axioms FX1Poly.Core.RawTermChildren.replaceChildAt?_etaRelated

end FX1PolyAudit
