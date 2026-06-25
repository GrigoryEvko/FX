import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.TableRootEtaSubjectReductionNative
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationEta
import FX1Poly.Core.Metatheory.Normalization.Orders.EtaRpoEmbedding

/-! # FX1PolyAudit/AuditTableRootEtaSubjectReductionNative — TABLE-CANON-ETA
re-base increment 1 shard

Per-declaration zero-axiom gate for the bespoke-construction-free
table-root-eta subject reduction and the natively-reproved SN/RPO size
twins.

The Core source-shape readers (`etaLamRowContraction_sourceShape` /
`etaPairRowContraction_sourceShape` / `etaPathLamRowContraction_sourceShape`,
each recovering the matching `RawTerm.etaXxxSource` shape WITHOUT a
`Step.eta`) and their total dispatcher (`stepEtaRootTableSourceShape`)
re-base the table relation's SR leg off the bespoke `Step.eta`
constructors.  The two size twins
(`Step.etaRootTable_size_decreases` and `StepEtaRootTable.rpoEmbeds`) are
now proved natively off those readers — they no longer cross the bespoke
adequacy bridge `stepEtaTableRootToBespokeEta`.  Must be free of
`propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.etaLamRowContraction_sourceShape
#assert_no_axioms FX1Poly.Core.etaPairRowContraction_sourceShape
#assert_no_axioms FX1Poly.Core.etaPathLamRowContraction_sourceShape
#assert_no_axioms FX1Poly.Core.stepEtaRootTableSourceShape
#assert_no_axioms FX1Poly.Core.Step.etaRootTable_size_decreases
#assert_no_axioms FX1Poly.Core.StepEtaRootTable.rpoEmbeds
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.preservedByTableEtaRootNative
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectReductionTableBetaEtaRootNative

end FX1PolyAudit
