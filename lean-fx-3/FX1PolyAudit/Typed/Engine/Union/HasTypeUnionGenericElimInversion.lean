import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Engine.Union.HasTypeUnionGenericElimInversion

/-! # FX1PolyAudit/HasTypeUnionGenericElimInversion — the table-driven elim-head inversion audit shard

Per-declaration zero-axiom gate for the ONE generic eliminator-head inversion (TYTAB-2, subsumes the 11
bespoke `invertAt<X>Head`) and its two rule-table disjointness helpers. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.introRuleOf_eq_none_ofElim
#assert_no_axioms FX1Poly.Typed.formationRuleOf_eq_none_ofElim
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.invertAtElimHeadGeneric

end FX1PolyAudit
