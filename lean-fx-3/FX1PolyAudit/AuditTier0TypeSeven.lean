import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Ledger.TypeAxis.TypeSeven

/-! # FX1PolyAudit/AuditTier0TypeSeven — zero-axiom gate for type-7 ★ (definitional univalence)

Per-declaration zero-axiom gate for `FX1Poly/Typed/Ledger/TypeAxis/TypeSeven.lean`: the four backed flips
(identity computation, identity canonicity, the equivalence type former, the definitional-univalence shape)
and the three deferral honesty markers (live definitional univalence, equivalence eliminators, univalent
universe).  Gating `fxType_definitionalUnivalenceShape_isBacked` transitively certifies the def-univalence
demonstrator + its confluence/orthogonality/SN certificates zero-axiom; gating
`fxType_identityCanonicity_isBacked` certifies the identity canonicity (`reflClosedReducesToValue` /
`idJCanonicalWitnessReducesToBase`); gating `fxType_equivalenceTypeFormer_isBacked` certifies the Equiv
reducible-member theorem.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The four backed flips
#assert_no_axioms FX1Poly.Tier0.fxType_hasIdentityComputation
#assert_no_axioms FX1Poly.Tier0.fxType_identityComputation_isBacked
#assert_no_axioms FX1Poly.Tier0.fxType_hasIdentityCanonicity
#assert_no_axioms FX1Poly.Tier0.fxType_identityCanonicity_isBacked
#assert_no_axioms FX1Poly.Tier0.fxType_hasEquivalenceTypeFormer
#assert_no_axioms FX1Poly.Tier0.fxType_equivalenceTypeFormer_isBacked
#assert_no_axioms FX1Poly.Tier0.fxType_hasDefinitionalUnivalenceShape
#assert_no_axioms FX1Poly.Tier0.fxType_definitionalUnivalenceShape_isBacked

-- The deferral honesty markers
#assert_no_axioms FX1Poly.Tier0.fxType_hasLiveDefinitionalUnivalence
#assert_no_axioms FX1Poly.Tier0.fxType_hasEquivalenceEliminators
#assert_no_axioms FX1Poly.Tier0.fxType_hasUnivalentUniverse

end FX1PolyAudit
