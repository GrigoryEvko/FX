import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Engine.Union.RawTermMorphismSubjectUsability

/-! # FX1PolyAudit.Typed.Engine.Union.RawTermMorphismSubjectUsability — zero-axiom gate (mirror shard)

The use-site usability transport (`isSubjectUsableAtModality` survives any raw-term morphism whose
variable images are usable) and the formation-obligation usability push family, each stated once
generically over the morphism. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.subjectUsabilityPreservedUnderMorphism
#assert_no_axioms FX1Poly.Typed.flatFormationObligations_usable_pushMorphism
#assert_no_axioms FX1Poly.Typed.termIndexedEndpointObligations_usable_pushMorphism
#assert_no_axioms FX1Poly.Typed.cumulativeFormationObligations_usable_pushMorphism
#assert_no_axioms FX1Poly.Typed.FormationRule.obligationsUsable_pushMorphism

end FX1PolyAudit
