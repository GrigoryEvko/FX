import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringEmptyMidSurvivorIdentity

/-! # FX1PolyAudit.…WalkingString.StringEmptyMidSurvivorIdentityAxiomWitness — INDEPENDENT axiom witness
(FC-3 r44, P2c partial)

The trusted independent cross-check for the empty-mid survivor-identity round: raw `#print axioms` on every
proof-carrying declaration (Lean's own kernel axiom-dependency prints, catching a `decide` degraded to
`sorryAx` and any `Lean.ofReduceBool` from `native_decide`).  Each must print `does not depend on any
axioms`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.emptyMidMatching_topPort_lt
#print axioms FX1Poly.Polygraph.emptyMidMatching_noForwardChord
#print axioms FX1Poly.Polygraph.stringEmptyMidMatching_isSurvivorIdentity
#print axioms FX1Poly.Polygraph.stringEmptyMidMatching_partnerComputesAtMidTwo
#print axioms FX1Poly.Polygraph.stringEmptyMidMatching_survivorIdentity_firesAtMidTwo
#print axioms FX1Poly.Polygraph.stringEmptyMidMatching_noForwardChord_firesAtMidTwo
#print axioms FX1Poly.Polygraph.fxString_hasEmptyMidSurvivorIdentity

end FX1PolyAudit
