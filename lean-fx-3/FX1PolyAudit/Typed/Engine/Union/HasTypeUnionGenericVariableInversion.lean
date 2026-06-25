import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Engine.Union.HasTypeUnionGenericVariableInversion

/-! # FX1PolyAudit/HasTypeUnionGenericVariableInversion — the variable-head inversion audit shard

Per-declaration zero-axiom gate for the generic native variable-head inversion (the `var`-surviving twin of
`invertAtElimHeadGeneric`; the foundational leaf of the native universe-flag-uniqueness keystone, #1697/#1740). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.HasTypeUnion.invertAtVarHeadGeneric

end FX1PolyAudit
