import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.TableCanonicalityFlip

/-! # FX1PolyAudit/AuditTableCanonicalityFlip — IOTA-T9 ★ flip shard

Per-declaration zero-axiom gate for the canonicality flip: the
legacy-relation derived-view embeddings (chains and conversion) and the
re-pointed canonical subject reduction.  Every declaration below must
be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## The legacy derived view -/

#assert_no_axioms FX1Poly.Core.StepStar.toStepTableClosure
#assert_no_axioms FX1Poly.Core.Conv.toConvTable
#assert_no_axioms FX1Poly.Core.ConvTable.ofLegacyConv

/-! ## ★★ The re-pointed canonical subject reduction -/

#assert_no_axioms FX1Poly.Core.StepTable.subjectReduction
#assert_no_axioms FX1Poly.Core.StepTable.subjectReductionStar

end FX1PolyAudit
