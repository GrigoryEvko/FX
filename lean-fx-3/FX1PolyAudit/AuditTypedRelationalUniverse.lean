import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Dimensions.Parametricity.RelationalUniverse

/-! # FX1PolyAudit/AuditTypedRelationalUniverse — zero-axiom gate for type-9 (the relational universe)

Per-declaration zero-axiom gate for `FX1Poly/Typed/Dimensions/Parametricity/RelationalUniverse.lean`: the
relational-universe object (`IsRelationalUniverseElement`), the "`Type` is the type of relations"
characterization (`binaryUniverse_isTypeOfRelations`), the reflexive-graph law on data types
(`relationalUniverseElement_reflexiveAtFlatData`), the identity-extension lemmas
(`binaryDataCandidate_diagonalIsUnary` / `binaryEmptyCandidate_diagonalIsUnary`), and the bridge-over-universe
internalization (`bridgeOverUniverse_isRelationalUniverseElement`).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.IsRelationalUniverseElement
#assert_no_axioms FX1Poly.Typed.binaryUniverse_isTypeOfRelations
#assert_no_axioms FX1Poly.Typed.relationalUniverseElement_reflexiveAtFlatData
#assert_no_axioms FX1Poly.Typed.binaryDataCandidate_diagonalIsUnary
#assert_no_axioms FX1Poly.Typed.binaryEmptyCandidate_diagonalIsUnary
#assert_no_axioms FX1Poly.Typed.bridgeOverUniverse_isRelationalUniverseElement

end FX1PolyAudit
