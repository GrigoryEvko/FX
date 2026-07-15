import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Engine.Union.HasTypeUnionFormationObligations

/-! # FX1PolyAudit.Typed.Engine.Union.HasTypeUnionFormationObligations — zero-axiom gate (mirror shard, region-D restructure) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.HasTypeUnion.formationRuleOfObligations
#assert_no_axioms FX1Poly.Typed.flatFormationObligations_pushSubst
#assert_no_axioms FX1Poly.Typed.termIndexedEndpointObligations_pushSubst
#assert_no_axioms FX1Poly.Typed.cumulativeFormationObligations_pushSubst
#assert_no_axioms FX1Poly.Typed.FormationRule.obligations_pushSubst
#assert_no_axioms FX1Poly.Typed.flatFormationObligations_pushRename
#assert_no_axioms FX1Poly.Typed.termIndexedEndpointObligations_pushRename
#assert_no_axioms FX1Poly.Typed.cumulativeFormationObligations_pushRename
#assert_no_axioms FX1Poly.Typed.FormationRule.obligations_pushRename
-- ★ A1-CONJUNCT-WIRE (#1829): the formation-arm use-site usability discharge over a lock-free context.
#assert_no_axioms FX1Poly.Typed.flatFormationObligations_usableOfLockFree
#assert_no_axioms FX1Poly.Typed.termIndexedEndpointObligations_usableOfLockFree
#assert_no_axioms FX1Poly.Typed.cumulativeFormationObligations_usableOfLockFree
#assert_no_axioms FX1Poly.Typed.FormationRule.obligationsUsableOfLockFree

end FX1PolyAudit
