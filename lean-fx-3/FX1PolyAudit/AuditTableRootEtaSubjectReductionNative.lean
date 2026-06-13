import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.TableRootEtaSubjectReductionNative

/-! # FX1PolyAudit/AuditTableRootEtaSubjectReductionNative — TABLE-CANON-ETA
re-base increment 1 shard

Per-declaration zero-axiom gate for the bespoke-construction-free
table-root-eta subject reduction: the Core source-shape reader
(`etaLamRowContraction_sourceShape`, which recovers the
`RawTerm.etaLamSource` shape WITHOUT a `Step.eta`), the native typed SR
dispatch (`preservedByTableEtaRootNative`), and the native union SR
(`subjectReductionTableBetaEtaRootNative`).  These re-base the table
relation's SR leg off the bespoke `Step.eta` constructors.  Must be free
of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.etaLamRowContraction_sourceShape
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.preservedByTableEtaRootNative
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectReductionTableBetaEtaRootNative

end FX1PolyAudit
