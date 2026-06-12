import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.TypedIdentificationTable

/-! # FX1PolyAudit/AuditTypedIdentificationTable — ETA-T6 inc-3 shard

Per-declaration zero-axiom gate for the type-directed identification
tier: the condition/rule schema, the canonical two rows (unit eta +
the ★ FX-novel grade-keyed ghost eta), the condition reader with its
symmetry, the `ConvOverIdentifications` judgmental extension, and the
basic metatheory (refl transfer, table monotonicity, conditional
empty-table conservativity, the per-row firing corollaries).  Must be
free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## Schema + canonical rows -/

#assert_no_axioms FX1Poly.Core.TypedIdentificationCondition
#assert_no_axioms FX1Poly.Core.TypedIdentificationRule
#assert_no_axioms FX1Poly.Core.unitIdentificationRule
#assert_no_axioms FX1Poly.Core.ghostIdentificationRule
#assert_no_axioms FX1Poly.Core.typedIdentificationTable
#assert_no_axioms FX1Poly.Core.unitIdentificationRule_memTable
#assert_no_axioms FX1Poly.Core.ghostIdentificationRule_memTable
#assert_no_axioms FX1Poly.Core.typedIdentificationTable_length

/-! ## The condition reader -/

#assert_no_axioms FX1Poly.Core.TypedIdentificationRule.ConditionHolds
#assert_no_axioms FX1Poly.Core.TypedIdentificationRule.ConditionHolds.symm

/-! ## The judgment + metatheory -/

#assert_no_axioms FX1Poly.Core.ConvOverIdentifications
#assert_no_axioms FX1Poly.Core.ConvOverIdentifications.refl
#assert_no_axioms FX1Poly.Core.ConvOverIdentifications.monotone
#assert_no_axioms FX1Poly.Core.ConvOverIdentifications.emptyTable_iff
#assert_no_axioms FX1Poly.Core.ConvOverIdentifications.unitIdentification
#assert_no_axioms FX1Poly.Core.ConvOverIdentifications.ghostIdentification

end FX1PolyAudit
