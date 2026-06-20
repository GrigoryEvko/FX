import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Metatheory.Canonicity.DataEliminatorCanonicity

/-! # FX1PolyAudit/AuditDataEliminatorCanonicity
    — zero-axiom gate for closed-scope recursive-data-eliminator canonicity (FTGEN-11.5)

`closedNatElimReducesToConstructor` / `closedNatRecReducesToConstructor`: a closed recursor cell built from
reducible pieces reduces to a constructor of its result type — the value-aware eliminator fundamental
theorem's computational payoff, via the recursion-discharged `*DataTaitMemberSelfContained` engine and
`dataTaitCandidate.closedReducesToValue`.  Must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.closedNatElimReducesToConstructor
#assert_no_axioms FX1Poly.Core.closedNatRecReducesToConstructor
#assert_no_axioms FX1Poly.Core.closedListElimReducesToConstructor
#assert_no_axioms FX1Poly.Core.closedBoolElimReducesToConstructor
#assert_no_axioms FX1Poly.Core.closedFstReducesToConstructor
#assert_no_axioms FX1Poly.Core.closedSndReducesToConstructor
#assert_no_axioms FX1Poly.Core.closedOptionMatchReducesToConstructor
#assert_no_axioms FX1Poly.Core.closedEitherMatchReducesToConstructor
#assert_no_axioms FX1Poly.Core.closedIdJReducesToConstructor
#assert_no_axioms FX1Poly.Core.closedIdStrictRecReducesToConstructor

end FX1PolyAudit
