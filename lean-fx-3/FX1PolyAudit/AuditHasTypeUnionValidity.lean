import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.Validity.HasTypeUnionValidity

/-! # FX1PolyAudit/AuditHasTypeUnionValidity — union classifier-validity zero-axiom gate

Per-declaration zero-axiom gate for `FX1Poly/Typed/Metatheory/Validity/HasTypeUnionValidity.lean`: the
union classifier-validity conclusion (`UnionClassifierIsType` + its constructors), the formation-output
helper, the two honest residual oracles (`UnionDataFormerValidity` / `UnionElimOutputValidity`), and the
main theorem `HasTypeUnion.classifierIsType`.  Every declaration below must be free of `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The conclusion predicate + its constructors.
#assert_no_axioms FX1Poly.Typed.UnionClassifierIsType
#assert_no_axioms FX1Poly.Typed.UnionClassifierIsType.ofUniverseCode
#assert_no_axioms FX1Poly.Typed.UnionClassifierIsType.ofBaseTypeRow
#assert_no_axioms FX1Poly.Typed.UnionClassifierIsType.ofFormationOutput

-- The two honest residual oracles.
#assert_no_axioms FX1Poly.Typed.UnionDataFormerValidity
#assert_no_axioms FX1Poly.Typed.UnionElimOutputValidity

-- ★ The main theorem: union classifier validity.
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.classifierIsType

end FX1PolyAudit
