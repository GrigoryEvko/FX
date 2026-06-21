import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionEmptyTypeCongruenceCloser

/-! # FX1PolyAudit/AuditUnionEmptyTypeCongruenceCloser — TYTAB-2-FT gate-2 empty-type congruence-closer audit

Per-declaration zero-axiom gate for the empty-type congruence closer reduced to the eliminator arm (gate-2
congruence half of TYTAB-2-FT, #1697): the bridge head-stability `headReaches_bridgeTypeCell`, the
eliminator-arm gate interface `UnionElimCongruenceClosesToEmptyType`, the generic context-threaded core
`congruenceClosesToEmptyTypeAux`, and the empty-context closer `congruenceClosesToEmptyTypeModuloElim`.  Each
must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.headReaches_bridgeTypeCell
#assert_no_axioms FX1Poly.Typed.variableCellHasNoCongruenceStep
#assert_no_axioms FX1Poly.Typed.universeCodeCellHasNoCongruenceStep
#assert_no_axioms FX1Poly.Typed.UnionElimCongruenceClosesToEmptyType
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.congruenceClosesToEmptyTypeAux
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.congruenceClosesToEmptyTypeModuloElim

end FX1PolyAudit
