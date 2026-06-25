import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Metatheory.Sconing.SconingTaitCrossLeg

/-! # FX1PolyAudit.Core.Metatheory.Sconing.SconingTaitCrossLeg

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Metatheory.Sconing.SconingTaitCrossLeg`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Cross-leg triangulation: the sconing leg and the Tait/Path-A leg produce SN over the SAME object — the
-- sconing-SN cell is bridged to Tait, not independent.  sconingScone_computable_eq_candidate: the sconing
-- witness's displayed predicate IS the reducibility candidate (rfl).  sconingScone_extraction_eq_candidateCR1:
-- the SN extraction IS CR1.  sconingSN_eq_taitComposition: for a well-typed term the sconing leg's extracted
-- SN is the identical witness CR1 (fundamental term typed) the Tait leg produces.  Genuine independence (a
-- second SN proof) would need a different `computable` — the synthetic STC logical relation — which the
-- shipped STC scaffold cannot supply zero-axiom (its ClosedMod is a one-constructor wrapper, not the HIT
-- closed modality, which pulls Quot.sound).  The STC ledger's logicalRelationConstruction rung is
-- witnessed by the BRIDGED construction (STC/FxLogicalRelation.lean — its semantic side is
-- definitionally the Tait pipeline, fxStcFundamental_semantic_isTaitWitness), and the
-- canonicityTheorem rung by the equally BRIDGED canonicityViaSTC (STC/FxBoolCanonicity.lean —
-- semantic side definitionally the kernel's closedBoolCanonicalForms); INDEPENDENCE remains
-- zero-axiom-blocked exactly as this note records, and the block is now FORMALIZED in
-- STC/FxIndependenceBoundary.lean (Prop-payload glues are syntax-determined; every inhabitant's
-- semantic component IS the kernel witness; the shipped ClosedMod is a definitional identity
-- retraction, not the HIT pushout).
#assert_no_axioms FX1Poly.Core.sconingScone_computable_eq_candidate

#assert_no_axioms FX1Poly.Core.normalizationScone_computable_eq_candidate

#assert_no_axioms FX1Poly.Core.sconingScone_and_normalizationScone_share_computable

#assert_no_axioms FX1Poly.Core.sconingScone_extraction_eq_candidateCR1

#assert_no_axioms FX1Poly.Core.sconingSN_eq_taitComposition

end FX1PolyAudit
