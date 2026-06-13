import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.TableBetaEtaRootConvAlgebra

/-! # FX1PolyAudit/AuditTableBetaEtaRootConvAlgebra — the TABLE-NATIVE
union beta-eta conversion algebra shard

Per-declaration zero-axiom gate for the purely-additive relational
algebra over the canonical union conversion `ConvTableBetaEtaRoot` — the
table-native mirror of the bespoke `BetaEtaConv` algebra
(`refl` / `sym` / `transAtTypedMiddle`):

* `refl` / `sym` — the structural join identity and chain-swap;
* `transAtTypedMiddle` — transitivity through a well-typed middle, the
  typed-fragment equivalence leg (native typed Church-Rosser at the
  peak);
* `eq_of_bothNormal` / `not_of_bothNormal_ne` — the union-normal
  discrimination helper and its contrapositive convenience form, the
  consumers' negative-witness shape.

Every gate must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.ConvTableBetaEtaRoot.refl
#assert_no_axioms FX1Poly.Typed.ConvTableBetaEtaRoot.sym
#assert_no_axioms FX1Poly.Typed.ConvTableBetaEtaRoot.transAtTypedMiddle
#assert_no_axioms FX1Poly.Typed.ConvTableBetaEtaRoot.eq_of_bothNormal
#assert_no_axioms FX1Poly.Typed.ConvTableBetaEtaRoot.not_of_bothNormal_ne

end FX1PolyAudit
