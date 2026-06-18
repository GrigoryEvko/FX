import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Ledger.TypeAxis.TypeFour

/-! # FX1PolyAudit/AuditTier0TypeFour — zero-axiom gate for type-4 (indexed W / IR / II)

Per-declaration zero-axiom gate for `FX1Poly/Typed/Ledger/TypeAxis/TypeFour.lean`: the four backed flips
(the well-scoped mutual syntax, the description-driven mutual typing judgment, the structural mutual decider,
the W-recursor reduct demo) and the three deferral honesty markers (object-level indexed W-types, induction-
recursion, induction-induction).  Gating `fxType_structuralMutualDecider_isBacked` here transitively certifies
the cited `IsTypeDesc.decidableOfWellFormedGeneric` decider zero-axiom; gating
`fxType_descriptionDrivenTyping_isBacked` certifies the `HasTypeDesc`/`DescTelescope` mutual derivation.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The four backed flips
#assert_no_axioms FX1Poly.Tier0.fxType_hasScopedSyntaxMutual
#assert_no_axioms FX1Poly.Tier0.fxType_scopedSyntaxMutual_isBacked
#assert_no_axioms FX1Poly.Tier0.fxType_hasDescriptionDrivenTyping
#assert_no_axioms FX1Poly.Tier0.fxType_descriptionDrivenTyping_isBacked
#assert_no_axioms FX1Poly.Tier0.fxType_hasStructuralMutualDecider
#assert_no_axioms FX1Poly.Tier0.fxType_structuralMutualDecider_isBacked
#assert_no_axioms FX1Poly.Tier0.fxType_hasWStyleRecursorDemo
#assert_no_axioms FX1Poly.Tier0.fxType_wStyleRecursorDemo_isBacked
#assert_no_axioms FX1Poly.Tier0.fxType_hasInductiveInductiveCrossRef
#assert_no_axioms FX1Poly.Tier0.fxType_inductiveInductiveCrossRef_isBacked

-- The deferral honesty markers
#assert_no_axioms FX1Poly.Tier0.fxType_hasIndexedWTypes
#assert_no_axioms FX1Poly.Tier0.fxType_hasInductionRecursion
#assert_no_axioms FX1Poly.Tier0.fxType_hasInductionInduction

end FX1PolyAudit
