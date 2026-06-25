import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Term.Action.InitialAlgebra

/-! # FX1PolyAudit/AuditTier0TermInitialAlgebra — zero-axiom gate for term-1 (the genuine initiality)

Per-declaration zero-axiom gate for `FX1Poly/Tier0/Term/Action/InitialAlgebra.lean`: RawTerm is the
initial algebra of its term signature — the carrier-general children spine `CarrierChildren`, the model
record `CarrierAlgebra`, the catamorphism `cata`/`cataChildren` + its `rfl` equations, the homomorphism
bundle `IsCarrierHomomorphism` with the mutual `unique`/`uniqueChildren` (uniqueness), the existence
witness `cataHomomorphism`, and the extensionality corollary `carrier_hom_ext`.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The signature functor's carrier-valued children + the model record
#assert_no_axioms FX1Poly.Core.CarrierChildren
#assert_no_axioms FX1Poly.Core.CarrierAlgebra

-- The catamorphism + its defining equations
#assert_no_axioms FX1Poly.Core.cata
#assert_no_axioms FX1Poly.Core.cataChildren
#assert_no_axioms FX1Poly.Core.cata_mkGen
#assert_no_axioms FX1Poly.Core.cataChildren_nil
#assert_no_axioms FX1Poly.Core.cataChildren_cons

-- The initial-algebra universal property: existence + uniqueness + extensionality
#assert_no_axioms FX1Poly.Core.IsCarrierHomomorphism
#assert_no_axioms FX1Poly.Core.IsCarrierHomomorphism.unique
#assert_no_axioms FX1Poly.Core.IsCarrierHomomorphism.uniqueChildren
#assert_no_axioms FX1Poly.Core.cataHomomorphism
#assert_no_axioms FX1Poly.Core.carrier_hom_ext

-- The remaining catamorphism laws (op-duals of term-3): Cata-FUSION + Cata-REFLECTION, completing the
-- standard three-law package and restoring the LEFT/RIGHT duality of the term axis.
#assert_no_axioms FX1Poly.Core.CarrierChildren.map
#assert_no_axioms FX1Poly.Core.cata_fusion
#assert_no_axioms FX1Poly.Core.CarrierChildren.toRawChildren
#assert_no_axioms FX1Poly.Core.selfAlgebra
#assert_no_axioms FX1Poly.Core.cata_selfAlgebra_id
#assert_no_axioms FX1Poly.Core.cataChildren_selfAlgebra_toRaw

end FX1PolyAudit
