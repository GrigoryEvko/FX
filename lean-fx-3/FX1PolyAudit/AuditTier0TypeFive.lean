import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Ledger.TypeAxis.TypeFive

/-! # FX1PolyAudit/AuditTier0TypeFive — zero-axiom gate for type-5 (QIITs as a presented schema)

Per-declaration zero-axiom gate for `FX1Poly/Typed/Ledger/TypeAxis/TypeFive.lean`: the four backed flips
(quotient computation rows, well-formed presentation, computational quotient, signature value) and the three
deferral honesty markers (object-level quotient type former, quotient equality law, the QIIT former).  Gating
`fxType_computationalQuotient_isBacked` transitively certifies `Conv.equivalence` (and hence raw confluence)
zero-axiom; gating `fxType_quotientComputationRows_isBacked` certifies the quotient iota rows.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The four backed flips
#assert_no_axioms FX1Poly.Tier0.fxType_hasQuotientComputationRows
#assert_no_axioms FX1Poly.Tier0.fxType_quotientComputationRows_isBacked
#assert_no_axioms FX1Poly.Tier0.fxType_hasWellFormedPresentation
#assert_no_axioms FX1Poly.Tier0.fxType_wellFormedPresentation_isBacked
#assert_no_axioms FX1Poly.Tier0.fxType_hasComputationalQuotient
#assert_no_axioms FX1Poly.Tier0.fxType_computationalQuotient_isBacked
#assert_no_axioms FX1Poly.Tier0.fxType_hasSignatureValue
#assert_no_axioms FX1Poly.Tier0.fxType_signatureValue_isBacked
#assert_no_axioms FX1Poly.Tier0.fxType_hasQuotientRowStructuralSafety
#assert_no_axioms FX1Poly.Tier0.fxType_quotientRowStructuralSafety_isBacked

-- The deferral honesty markers
#assert_no_axioms FX1Poly.Tier0.fxType_hasQuotientTypeFormer
#assert_no_axioms FX1Poly.Tier0.fxType_hasQuotientEquality
#assert_no_axioms FX1Poly.Tier0.fxType_hasQuotientInductiveInductive

end FX1PolyAudit
