import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringPositiveMidLastCupShortChord

/-! # FX1PolyAudit.…WalkingString.StringPositiveMidLastCupShortChordAxiomWitness — INDEPENDENT axiom witness
(FC-3 r44, P2b)

The trusted independent cross-check for the positive-mid last-cup short-chord round: raw `#print axioms` on
every proof-carrying declaration.  Not the fuel-based `#assert_no_axioms` macro (that lives in the sibling
gate file) — these are Lean's own kernel axiom-dependency prints, which surface a `decide` silently degraded
to `sorryAx` and any `Lean.ofReduceBool` from a `native_decide`.  Each must print `does not depend on any
axioms`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.stringMatchingLastCup_isShortChord_mid
#print axioms FX1Poly.Polygraph.stringMidOneCupOverG_matchingComputes
#print axioms FX1Poly.Polygraph.stringMidTwoCupOverGH_matchingComputes
#print axioms FX1Poly.Polygraph.stringMatchingLastCupShortChord_mid_firesAtMidOne
#print axioms FX1Poly.Polygraph.stringMatchingLastCupShortChord_mid_firesAtMidTwo
#print axioms FX1Poly.Polygraph.fxString_hasPositiveMidLastCupShortChord

end FX1PolyAudit
