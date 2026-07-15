import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Engine.Union.RawTermMorphismFormationObligations

/-! # FX1PolyAudit.Typed.Engine.Union.RawTermMorphismFormationObligations — zero-axiom gate (mirror shard)

The formation-obligation push family stated ONCE, generically over any raw-term
morphism.  The renaming / substitution twins in `HasTypeUnionFormationObligations`
are instantiations of these and are gated in their own shard. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.flatFormationObligations_pushMorphism
#assert_no_axioms FX1Poly.Typed.termIndexedEndpointObligations_pushMorphism
#assert_no_axioms FX1Poly.Typed.cumulativeFormationObligations_pushMorphism
#assert_no_axioms FX1Poly.Typed.FormationRule.obligations_pushMorphism

end FX1PolyAudit
